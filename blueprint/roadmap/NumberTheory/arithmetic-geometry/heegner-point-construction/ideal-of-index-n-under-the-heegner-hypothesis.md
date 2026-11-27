# An ideal of index $N$ under the Heegner hypothesis

Let $K$ be an imaginary quadratic field with ring of integers $\mathcal{O}_K$ and let $N \ge 1$ be an integer such that
every prime factor of $N$ splits in $K$. Then there is an ideal $\mathcal{N}$ of $\mathcal{O}_K$ such that the
additive group $\mathcal{O}_K / \mathcal{N}$ is cyclic of order $N$.

Miller and Gross assert this without proof. An argument (worked out here, not in the sources): write
$N = \prod_p p^{e_p}$ and $p \mathcal{O}_K = \mathfrak{p} \bar{\mathfrak{p}}$ with $\mathfrak{p} \ne \bar{\mathfrak{p}}$ for
each $p \mid N$, and take $\mathcal{N} = \prod_p \mathfrak{p}^{e_p}$. As $\mathfrak{p}^{e_p} \cap \mathbb{Z} = p^{e_p}\mathbb{Z}$
(an element of $p^{k}\mathbb{Z} \setminus p^{k+1}\mathbb{Z}$ has $\mathfrak{p}$-adic valuation $k$), the map
$\mathbb{Z}/p^{e_p} \to \mathcal{O}_K/\mathfrak{p}^{e_p}$ is injective, and it is onto because both groups have
order $p^{e_p}$, the norm of $\mathfrak{p}^{e_p}$; the Chinese remainder theorem then gives
$\mathcal{O}_K/\mathcal{N} \cong \mathbb{Z}/N\mathbb{Z}$.

## Sources

- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero
  and one*, LMS J. Comput. Math. 14 (2011), 327–350, doi:10.1112/S1461157011000180: §4, p. 335 ("By hypothesis, there is an ideal $\mathcal{N}$ of $\mathcal{O}_K$ such that
  $\mathcal{O}_K/\mathcal{N}$ is cyclic of order $N$."), for $K$ satisfying the Heegner hypothesis (every
  $p \mid N$ splits in $K$).
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235 ("Choose an ideal $\mathcal{N}$ of $\mathcal{O}$ with $\mathcal{O}/\mathcal{N} \simeq \mathbb{Z}/N\mathbb{Z}$.").
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Proposition 3.8 and Hypothesis 3.9, p. 35, the same condition in terms of the orders embedded in $M_0(N)$.
