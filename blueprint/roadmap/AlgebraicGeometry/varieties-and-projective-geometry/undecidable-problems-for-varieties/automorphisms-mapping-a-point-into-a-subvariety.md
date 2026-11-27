# Whether an automorphism of a variety maps a point into a subvariety is undecidable

No algorithm decides, given a smooth projective geometrically integral complex variety $X$, a closed point $x \in X$ and a smooth projective geometrically integral subvariety $Z \subseteq X$, whether some automorphism of $X$ maps $x$ into $Z$; this holds even for one fixed $X$ and $x$ defined over $\mathbb{Q}$.

**Setting (Poonen).** A *variety* over a field $k$ is a separated scheme of finite type over $k$, and it is *nice* if it is smooth, projective and geometrically integral. So that inputs are finite objects, a complex variety is given by equations whose coefficients lie in a finitely generated subfield $K \subseteq \mathbb{C}$, itself given as the fraction field of $\mathbb{Z}[x_1, \dots, x_n]/(f_1, \dots, f_m)$ for explicit $f_i \in \mathbb{Z}[x_1, \dots, x_n]$ generating a prime ideal, with elements of $K$ written as rational expressions in the generators. $\operatorname{Aut} X$ is the group of automorphisms of $X$ as a variety.

**Theorem (Poonen).** There is no algorithm that, given a nice complex variety $X$, a closed point $x \in X$ and a nice subvariety $Z \subseteq X$, decides whether there is an automorphism of $X$ mapping $x$ into $Z$ (Theorem 1.1 of arXiv:0902.3571v1).

The source also proves a uniform version: there are a fixed nice $\mathbb{Q}$-variety $X$ and a fixed rational point $x \in X(\mathbb{Q})$ such that no algorithm decides, given a nice $\mathbb{Q}$-subvariety $Z \subseteq X$, whether $Z$ meets the orbit $\{\sigma x : \sigma \in \operatorname{Aut} X\}$ (Theorem 1.2 of arXiv:0902.3571v1); for this $X$, $\operatorname{Aut} X = \operatorname{Aut} X_{\mathbb{C}}$, so it does not matter whether automorphisms defined over $\mathbb{Q}$ or over $\mathbb{C}$ are allowed.

Both problems are decidable when $X$ is a nice variety of general type, since then $\operatorname{Aut} X$ is finite and computable (Remark 1.3 of the source). Along the way the source proves that Hilbert's tenth problem stays undecidable for systems $f_1, \dots, f_m \in \mathbb{Z}[x_1, \dots, x_n]$ whose affine $\mathbb{Q}$-variety has smooth, geometrically integral projective closure in $\mathbb{P}^n_{\mathbb{Q}}$ (Corollary 4.3 of arXiv:0902.3571v1).

## Depends on

- [Geometrically reduced variety over a field](../../schemes-and-morphisms/varieties-over-a-field/is-variety.md)
- [Smooth morphisms of schemes](../../schemes-and-morphisms/smooth-morphisms/smooth-morphism-of-schemes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Fix an elliptic curve $E$ over $\mathbb{Q}$ with $\operatorname{End} E \cong \mathbb{Z}$ and a rational point $P$ of infinite order, and $n \ge 3$. For a finite set $S \subseteq \mathbb{Z}^n$ containing $\vec 0$ whose stabilizer in $\mathrm{GL}_n(\mathbb{Z}) \ltimes \mathbb{Z}^n$ is the group of matrices with identity upper-left block, last column $(a_1, \dots, a_n)$ and $a_n = \pm 1$ (Lemma 2.1), let $X$ be the blowup of $E^n$ at the corresponding finite set of points of $(\mathbb{Z} P)^n$. Through the Albanese map $X \to E^n$, every automorphism of $X$ comes from an automorphism of $E^n$ preserving the blown-up set, and $\operatorname{Aut} E^n = \mathrm{GL}_n(\mathbb{Z}) \ltimes E^n(\mathbb{C})$ because $\operatorname{End} E = \mathbb{Z}$. The orbit of a suitable point $x$ then corresponds to an explicit subset of $\mathbb{Z}^{n-1}$, and asking whether a subvariety cut out from a Diophantine polynomial meets it is equivalent to solvability of that polynomial in integers; making the subvariety nice uses resolution of singularities and the smooth version of Hilbert's tenth problem (Section 4). A complete expansion links pages for the universal property of the Albanese map of a blowup, the description of the automorphism group of a power of an elliptic curve without complex multiplication, and Hironaka's resolution of singularities in characteristic zero, which have none.

## Sources

- B. Poonen, "Automorphisms mapping a point into a subvariety", *Journal of Algebraic Geometry* 20(4):785–794, 2011, doi:[10.1090/S1056-3911-2011-00543-2](https://doi.org/10.1090/S1056-3911-2011-00543-2); read as arXiv:0902.3571v1 ([arXiv](https://arxiv.org/abs/0902.3571v1)), whose numbering is used: Theorems 1.1 and 1.2 with the conventions of Section 1, Lemma 2.1, Section 3 and Corollary 4.3.
