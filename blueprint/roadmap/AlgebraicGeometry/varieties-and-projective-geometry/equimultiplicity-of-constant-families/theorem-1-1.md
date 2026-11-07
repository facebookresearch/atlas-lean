# Equimultiplicity of μ-constant families

Let $n \in \mathbb{N}$ and let $(f_t)_{t \in [0,1]}$
be a family of formal power series in $\mathbb{C}[[z_1, \dots, z_n]]$ such that each coefficient
of $f_t$ depends continuously on $t$ and each $f_t$ has zero constant term. If there is a natural
number $\mu$ such that the Milnor number of $f_t$ equals $\mu$ for every $t$, then the order of
$f_t$ (the least total degree of a monomial with nonzero coefficient, $\infty$ if $f_t = 0$) is
the same for all $t \in [0,1]$.

The paper calls this order the multiplicity of $f_t$. Its Theorem 1.1 does not state that the
constant terms vanish, but the hypothesis is needed: it says that each $f_t$ is a germ
$(\mathbb{C}^n, 0) \to (\mathbb{C}, 0)$, as in the paper's abstract and Corollary 1.3. For $n = 1$
and $f_t = z_1 + t$ the Milnor number is $0$ for every $t$, since the ideal of partial derivatives
contains $1$, while $f_0$ has order $1$ and $f_1$ has order $0$.

## Sources

- J. Fernández de Bobadilla and T. Pełka, `Symplectic monodromy at radius zero and equimultiplicity of μ-constant families`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-SymplecticMonodromy.lean Via leanprover/lean-eval@38361be, problem `annals_symplectic_monodromy`.
