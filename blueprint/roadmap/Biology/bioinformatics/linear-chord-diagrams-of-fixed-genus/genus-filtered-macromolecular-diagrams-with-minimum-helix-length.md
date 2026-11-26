# Genus-filtered macromolecular diagrams with minimum helix length

**Setting.** A **linear chord diagram** with $n$ chords is a perfect matching of $2n$ points on a horizontal backbone, drawn as arcs in the upper half-plane. Collapsing the backbone to a single vertex makes it a fatgraph with one vertex and $n$ edges; if it has $r$ boundary components, its **genus** $g$ satisfies $r=n+1-2g$. Let $\mathbf c_g(n)$ count linear chord diagrams of genus $g$ with $n$ chords and $\mathbf C_g(z)=\sum_{n\ge0}\mathbf c_g(n)z^n$; genus-$0$ diagrams are noncrossing and $\mathbf c_0(n)$ is the Catalan number. In RNA terms, chords are base pairs and genus $g\ge1$ measures the topological complexity of pseudoknots. A *partial* linear chord diagram allows isolated backbone vertices. A *1-chord* joins adjacent vertices. Two chords $(i_1,j_1)$ and $(i_2,j_2)$ are consecutively parallel if $i_1=i_2-1$ and $j_2=j_1-1$; the equivalence classes generated are *stacks* (helices). A **macromolecular diagram of minimum helix length $\sigma\ge1$** on $n$ vertices is a partial linear chord diagram with no 1-chords in which every stack has at least $\sigma$ chords. Let $\mathbf d_{g,\sigma}(n)$ count those of genus $g$ and $\mathbf D_{g,\sigma}(z)=\sum_n\mathbf d_{g,\sigma}(n)z^n$. A *shape* is a linear chord diagram whose stacks are single chords; $\mathbf S_g(z,u)$ is the bivariate generating function of genus-$g$ shapes by chords ($z$) and 1-chords ($u$).

**Lemma (shapes).** For $g\ge0$,

$$
\mathbf S_g(z,u)=\frac{1+z}{1+2z-zu}\,\mathbf C_g\!\left(\frac{z(1+z)}{(1+2z-zu)^2}\right).
$$

**Theorem.** For positive integers $g,\sigma$ let $u_\sigma(z)=\dfrac{z^{2(\sigma-1)}}{z^{2\sigma}-z^2+1}$. Then $\mathbf D_{g,\sigma}(z)$ is algebraic and

$$
\mathbf D_{g,\sigma}(z)=\frac{1}{u_\sigma(z)z^2-z+1}\,\mathbf C_g\!\left(\frac{u_\sigma(z)z^2}{\bigl(u_\sigma(z)z^2-z+1\bigr)^2}\right).
$$

In particular, for fixed $g$ and $\gamma_2\approx1.9685$,

$$
[z^n]\,\mathbf D_{g,2}(z)\sim k_g\,n^{3(g-\frac12)}\,\gamma_2^{\,n}
$$

for some constant $k_g$: the exponential growth rate of genus-$g$ structures with helices of length at least two does not depend on the genus, and genus only changes the polynomial factor.

## Depends on

- [Genus recursion and generating function of linear chord diagrams](genus-recursion-and-generating-function-of-linear-chord-diagrams.md)

## Expansion

Collapsing every stack to a single chord and contracting backbone segments projects each diagram onto a unique shape of the same genus. Linear chord diagrams with $m$ marked 1-chords inflate shapes by replacing chords with stacks, which inverts to the shape formula by substituting into $\mathbf C_g$. A macromolecular diagram is recovered from its shape by inflating each chord into a sequence of stacks of length at least $\sigma$ separated by nonempty unpaired intervals and inserting unpaired intervals into the $2s+1$ gaps, with a mandatory insertion inside each 1-chord of the shape; the symbolic method gives a rational substitution into $\mathbf S_g$ and hence into $\mathbf C_g$. Since $\mathbf C_g$ has its only singularity at $1/4$, the dominant singularity of $\mathbf D_{g,\sigma}$ is the root of the substituted argument reaching $1/4$, independent of $g$, while the exponent $\frac12-3g$ of $(1-4z)$ produces the factor $n^{3g-3/2}$.

## Sources

- J. E. Andersen, R. C. Penner, C. M. Reidys and M. S. Waterman, "Enumeration of linear chord diagrams", arXiv (2010), Section 2.5 "Topological Filtrations and Generating Functions" (shapes, projection, macromolecular diagrams) and Section 4 "Macromolecular diagrams of genus $g$" (shape lemma, inflation lemma and main theorem), <https://doi.org/10.48550/arXiv.1010.5614>
