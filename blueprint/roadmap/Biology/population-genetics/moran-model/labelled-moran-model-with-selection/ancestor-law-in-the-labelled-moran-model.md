# Ancestor law and fixation probabilities in the labelled Moran model

**Moran model with selection.** A haploid population of fixed size $N$ has types $A$ (reproducing at rate $1+s_N$, $s_N \ge 0$) and $B$ (rate $1$); each offspring replaces a uniformly chosen individual. Let $h_i^N$ be the probability that type $A$ fixes when started from $i$ type-$A$ individuals.

**Labelled Moran model.** Individuals carry labels $1,\dots,N$, initially one of each. Neutral arrows occur at rate $1/N$ per ordered pair of lines irrespective of labels; selective arrows occur at rate $s_N/N$ per ordered pair but only from a label $i$ to a label $j > i$. Thus every label is "more fit" towards higher labels and "less fit" towards lower ones. Declaring labels $\{1,\dots,i\}$ to be type $A$ and the rest type $B$ reproduces the type-frequency process of the Moran model started from $i$ type-$A$ individuals, for every $i$ simultaneously. Without mutation one label, the **ancestor** $I^N$, eventually fixes.

**Theorem.** The ancestor has law

$$\eta_i^N := \mathbb P(I^N = i) = (1+s_N)^{N-i}\,\eta_N^N = h_i^N - h_{i-1}^N, \qquad 1 \le i \le N,$$

$$\eta_N^N = \frac{1}{\sum_{j=0}^{N-1}(1+s_N)^j} = 1 - h^N_{N-1},$$

so that $h_i^N = \mathbb P(I^N \le i)$.

**Selective defining events.** Call an arrow *defining* if it emanates from $\{1,\dots,I^N\}$ and hits a line in $\{I^N+1,\dots,N\}$ that is not an external descendant of those labels; each is selective with probability $s_N/(1+s_N)$, independently. Let $Y^N$ be the number of selective defining events. Then $Y^N + 1$ is distributed as a $\mathrm{Bin}\big(N, s_N/(1+s_N)\big)$ variable conditioned to be positive, and

$$\mathbb P(I^N = i \mid Y^N = n) = \binom{N-i}{n}\Big/\binom{N}{n+1}, \qquad h_i^N = \sum_{n=0}^{N-1}\Big[\binom{N}{n+1} - \binom{N-i}{n+1}\Big] s_N^n\, \eta_N^N.$$

## Depends on

- [Fixation probability of the Moran process](../moran-fixation.md)

## Expansion

The label order turns the selection asymmetry into a monotone coupling: lumping labels $\le i$ into type $A$ gives the original model for each $i$ at once, so $\mathbb P(I^N \le i) = h_i^N$, and the ratio $\eta_i^N/\eta_{i+1}^N = 1+s_N$ is the relative weight of a label against its upper neighbor. The theorem recovers $h_i^N = \big(1-(1+s_N)^{-i}\big)/\big(1-(1+s_N)^{-N}\big)$ with elementary arguments. Each of the $N - I^N$ higher lines must be taken over once by a defining event, and these events are independently selective or neutral; this explains the binomial law of $Y^N$ and the hypergeometric-type conditional law of the ancestor given the number of selective events. The representation also yields an algorithm sampling the ancestor together with the positions hit by selective defining events, i.e. the ancestral line forward in time.

## Sources

- Sandra Kluth, Ellen Baake, "The Moran model with selection: fixation probabilities, ancestral lines, and an alternative particle representation", *Theoretical Population Biology* 90 (2013), 104–112, <https://doi.org/10.1016/j.tpb.2013.09.009>; preprint arXiv:1306.2772, <https://doi.org/10.48550/arXiv.1306.2772>. Numbering of the arXiv version: Section 2 (model), Section 4 (labelled Moran model, Theorem 1), Section 5 (defining events, Proposition 1 and the conditional ancestor law), Section 6 (Algorithm 1).
