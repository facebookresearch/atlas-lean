# Covering lemma

Let $P_{A,B}$ be a joint distribution, let $(A_j, B_j)$ be independent and identically distributed according to
$P_{A,B}$, and let $F_n \subseteq \mathcal{A}^n \times \mathcal{B}^n$. If $R > I(A;B)$ and a codebook of $M = 2^{nR}$
codewords is drawn independently from $P_B^{\otimes n}$, independently of $A^n$, then

$$\Pr[\exists \text{ codeword } c : (A^n, c) \in F_n] \ge \Pr[(A^n, B^n) \in F_n] + o(1) \quad (n \to \infty).$$


## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Joint typicality (finite iid).

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft), Theorem 25.5 (covering lemma). <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
