# Freiman's theorem

For every constant $C$ there are $d_0$ and $K$ such that every nonempty finite set $A \subseteq \mathbb{Z}$ with $|A + A| \le C|A|$ is contained in a $d$-dimensional arithmetic progression

$$\Bigl\{x_0 + \sum_{i=1}^d a_i x_i : 0 \le a_i < k_i\Bigr\}$$

with $d \le d_0$, positive integers $x_i, k_i$ and size $k_1 \cdots k_d \le K|A|$. This is Freiman's theorem as stated in Theorem 7.1 of Gowers's paper, where Ruzsa's proof (with reasonable bounds) is cited; Gowers adds that the same holds when $|A - A| \le C|A|$. The nonemptiness hypothesis is implicit there: the size bound fails for $A = \emptyset$.

The Plünnecke–Ruzsa inequalities are the standard sumset estimates of Ruzsa's approach; Gowers's Lemma 7.7 is a variant of the Bogolyubov argument that Ruzsa used in his proof.

## Background

- [Polynomial Freiman–Ruzsa theorem](../polynomial-freiman-ruzsa-theorem/README.md): the polynomial-bounds form over $\mathbb{F}_2^n$, proved by Gowers, Green, Manners and Tao.
- [Balog–Szemerédi–Gowers theorem](balog-szemeredi-gowers.md): the passage from many additive quadruples to small doubling, after which Freiman's theorem applies.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Theorem 7.1.
- W. T. Gowers, "Decompositions, approximate structure, transference, and the Hahn–Banach theorem", Bull. London Math. Soc. 42 (2010), 573–606; numbering of arXiv:0811.3103, Theorem 2.6.
