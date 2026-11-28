# A proper ideal times its conjugate

Let $\omega \in \mathbb{C}$ be non-real and let
$\mathcal{O} \subseteq \mathbb{C}$ be a subring whose underlying set is the lattice
$\mathbb{Z} + \mathbb{Z}\omega$, an order in an imaginary quadratic field. Let $\mathfrak{a}$ be the
lattice of a period pair $L$ that is a proper ideal of $\mathcal{O}$ (its endomorphism ring
$\{\lambda \in \mathbb{C} : \lambda\mathfrak{a} \subseteq \mathfrak{a}\}$ is $\mathcal{O}$) and is
contained in $\mathcal{O}$, and let $N = [\mathcal{O} : \mathfrak{a}]$ be its index. Then, with
$\bar{\mathfrak{a}}$ the complex conjugate lattice and products of $\mathbb{Z}$-submodules of
$\mathbb{C}$,

$$\mathfrak{a}\bar{\mathfrak{a}} = N\mathcal{O},$$

$N \neq 0$, and $\mathfrak{a} \cdot N^{-1}\bar{\mathfrak{a}} = \mathcal{O}$, so $\mathfrak{a}$ is
invertible with inverse $N^{-1}\bar{\mathfrak{a}}$.

No imaginary quadratic field is fixed in advance, and $\mathfrak{a}$ need not lie in one: properness
alone puts it, up to homothety, in $\mathbb{Q}(\omega)$.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lecture 17, Theorem 17.10 and its proof ($\mathfrak{a}\bar{\mathfrak{a}} = (N\mathfrak{a})$ and $\mathfrak{a}^{-1} = \frac{1}{N\mathfrak{a}}\bar{\mathfrak{a}}$ for a proper $\mathcal{O}$-ideal), and Lecture 16, Definition 16.9 (proper ideals); the reduction to `PeriodPair.lattice_mul_map_conj_eq_relIndex_smul` is written out here.
