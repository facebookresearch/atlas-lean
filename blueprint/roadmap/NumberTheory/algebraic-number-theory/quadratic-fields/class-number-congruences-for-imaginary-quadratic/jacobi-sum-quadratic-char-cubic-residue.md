# Jacobi sums of the quadratic and the cubic residue character

Let $K$ be a number field
generated over $\mathbb{Q}$ by a primitive cube root of unity, with ring of integers
$\mathcal{O}_K$. Let $\mu \in \mathcal{O}_K$ with $\mu \equiv 1 \pmod 3$, and let $p$ be a prime
such that the norm of $\mu$ from $\mathcal{O}_K$ to $\mathbb{Z}$ is $p$. Let
$\chi : \mathbb{Z}/p\mathbb{Z} \to \mathcal{O}_K$ be a multiplicative character with
$\chi(t) \equiv t^{(p-1)/3} \pmod{\mu}$ for every integer $t$ (the cubic residue character modulo
$\mu$), and let $\phi$ be the quadratic character of $\mathbb{Z}/p\mathbb{Z}$, with values in
$\{0, \pm 1\} \subset \mathcal{O}_K$. Writing
$J(\alpha, \beta) = \sum_{t \in \mathbb{Z}/p\mathbb{Z}} \alpha(t)\,\beta(1 - t)$, one has
$J(\phi, \chi) = \chi(4)\,J(\chi, \chi)$ and $J(\chi, \chi) = -\mu$.

The source states this for arbitrary characters $\phi$ and $\chi$ of $\mathbb{F}_p^\times$; the
identity holds for the quadratic $\phi$ and the cubic residue character $\chi$ modulo $\mu$, the
characters of the lemma it cites (Ireland-Rosen, Chap. 18, §3 and Chap. 9, §4).

## Sources

- Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26 (2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (a).
