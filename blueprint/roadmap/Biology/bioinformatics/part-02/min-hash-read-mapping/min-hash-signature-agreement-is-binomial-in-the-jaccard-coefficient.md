# Min-hash signature agreement is binomial in the Jaccard coefficient

**Setting.** Let $\Sigma=\{A,C,G,T\}$, fix $q\ge1$, and let $\Sigma^q$ be the set of all $q$-grams, linearly ordered (for example lexicographically). For a DNA string (a read, or a window of the reference genome) let $Q\subseteq\Sigma^q$ be its set of $q$-grams. For a permutation $\pi$ of $\Sigma^q$ the **min-hash** $h_\pi(Q)$ is the element of $Q$ that comes first in the order $\pi$. For permutations $\pi_1,\dots,\pi_s$ the **signature** of $Q$ is $\big(h_{\pi_1}(Q),\dots,h_{\pi_s}(Q)\big)$.

**Theorem.** Let $Q,Q'\subseteq\Sigma^q$ be nonempty, let $J=J(Q,Q')=|Q\cap Q'|/|Q\cup Q'|$ be their Jaccard coefficient, and let $\pi_1,\dots,\pi_s$ be independent, each uniformly distributed on the permutations of $\Sigma^q$. Then the number $K$ of coordinates on which the signatures of $Q$ and $Q'$ agree, $K=\#\{r\le s: h_{\pi_r}(Q)=h_{\pi_r}(Q')\}$, has the binomial law $\mathrm{Binomial}(s,J)$. Consequently $K/s$ is an unbiased estimator of $J$ with variance $J(1-J)/s$.

## Expansion

For a single uniform permutation, the [MinHash collision probability](../../../../ComputerScience/randomized-algorithms/minhash-and-jaccard-similarity/uniform-on-min-hash-collision.md) gives $\Pr[h_\pi(Q)=h_\pi(Q')]=J$; it applies with the finite linearly ordered universe $U=\Sigma^q$, the sets $Q,Q'$ have nonempty union, and the minimum ranks coincide exactly when the minimisers coincide because $\pi$ is injective. The events $\{h_{\pi_r}(Q)=h_{\pi_r}(Q')\}$, $r=1,\dots,s$, are independent because the $\pi_r$ are, so $K$ is a sum of $s$ independent Bernoulli$(J)$ indicators. In the variant-tolerant mapper of Quedenfeld and Rahmann, a read is mapped by looking up each signature coordinate in an index from signature values to reference windows and ranking windows by their number of hits, that is, by $K$. Sequencing errors or variants change only the $q$-grams overlapping the affected positions (at most $q$ per substitution), so $J$ degrades gracefully; known variants are made visible by inserting into the index the signature values of the variant-containing versions of a window. In practice true random permutations of $4^q$ elements are infeasible to store, so implementations use a random machine word $\pi$ and $h_\pi(Q)=\min\{x\oplus\pi : x\in Q\}$ over hashed $q$-grams; this XOR scheme only approximates the lemma (it is not min-wise independent) but behaves well empirically. Refereed min-hash read mappers, such as MashMap (Jain et al.), likewise estimate the Jaccard coefficient between a read and reference windows from min-hash sketches and use the resulting sampling distribution to choose mapping thresholds.

## Proof depends on

- [MinHash collision probability](../../../../ComputerScience/randomized-algorithms/minhash-and-jaccard-similarity/uniform-on-min-hash-collision.md)

## Sources

- J. Quedenfeld and S. Rahmann, "Variant tolerant read mapping using min-hashing", arXiv:1702.01703 (2017), Section 2 (Lemma "Min-hash property", Eq. for XOR signatures), <https://doi.org/10.48550/arXiv.1702.01703>.
- C. Jain, A. Dilthey, S. Koren, S. Aluru, A. M. Phillippy, "A Fast Approximate Algorithm for Mapping Long Reads to Large Reference Databases", Journal of Computational Biology 25 (2018), 766–779 (min-hash Jaccard estimation for read mapping), <https://doi.org/10.1089/cmb.2018.0036>.
- A. Z. Broder, "On the resemblance and containment of documents", Proceedings of Compression and Complexity of Sequences (1997), 21–29, <https://doi.org/10.1109/SEQUEN.1997.666900>.
