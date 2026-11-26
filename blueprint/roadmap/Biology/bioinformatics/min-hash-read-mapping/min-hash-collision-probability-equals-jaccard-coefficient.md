# Min-hash collision probability equals the Jaccard coefficient

**Setting.** Let $\Sigma=\{A,C,G,T\}$, fix $q\ge1$, and let $\Sigma^q$ be the set of all $q$-grams. For a DNA string (a read, or a window of the reference genome) let $Q\subseteq\Sigma^q$ be its set of $q$-grams. For a permutation $\pi$ of $\Sigma^q$ define the **min-hash** $h_\pi(Q)=\min_\pi Q$, the element of $Q$ that comes first in the order $\pi$.

**Lemma (min-hash property).** If $\pi$ is drawn uniformly from all permutations of $\Sigma^q$, then for any nonempty $Q,Q'\subseteq\Sigma^q$,

$$
\Pr\bigl[h_\pi(Q)=h_\pi(Q')\bigr] = J(Q,Q') = \frac{|Q\cap Q'|}{|Q\cup Q'|}.
$$

**Consequence for mapping.** With $s$ independent permutations $\pi_1,\dots,\pi_s$ (the **signature** of length $s$), the number of agreeing coordinates between the signatures of a read and a window is $\mathrm{Binomial}(s,J)$, so its fraction is an unbiased estimator of the Jaccard similarity with variance $J(1-J)/s$. A read is mapped by looking up each signature coordinate in an index from signature values to reference windows and ranking windows by their number of hits. Sequencing errors or variants change only the $q$-grams overlapping the affected positions (at most $q$ per substitution), so $J$ degrades gracefully; known variants are made visible by inserting into the index the signature values of the variant-containing versions of a window.

## Expansion

All elements of $Q\cup Q'$ are equally likely to be the $\pi$-minimum of $Q\cup Q'$. The two min-hashes coincide exactly when that minimum lies in $Q\cap Q'$: then it is the minimum of both sets; if instead it lies in only one set, that set's min-hash is an element the other set lacks, so they differ. Hence the collision probability is $|Q\cap Q'|/|Q\cup Q'|$. In practice true random permutations of $4^q$ elements are infeasible to store, so implementations use a random machine word $\pi$ and $h_\pi(Q)=\min\{x\oplus\pi : x\in Q\}$ over hashed $q$-grams; this XOR scheme only approximates the lemma (it is not min-wise independent) but behaves well empirically.

## Sources

- J. Quedenfeld and S. Rahmann, "Variant tolerant read mapping using min-hashing", arXiv:1702.01703 (2017), Section 2 (Lemma "Min-hash property", Eq. for XOR signatures), <https://doi.org/10.48550/arXiv.1702.01703>.
- A. Z. Broder, "On the resemblance and containment of documents", Proceedings of Compression and Complexity of Sequences (1997), 21–29, <https://doi.org/10.1109/SEQUEN.1997.666900>.
