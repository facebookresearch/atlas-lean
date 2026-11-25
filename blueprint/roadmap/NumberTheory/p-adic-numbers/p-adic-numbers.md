# The field of p-adic numbers

Fix a prime $p$, and let $|\cdot|_p$ be the $p$-adic absolute value on $\mathbb{Q}$: $|0|_p = 0$, and $|x|_p = p^{-v}$ when $x = p^{v} a/b$ with $v \in \mathbb{Z}$ and integers $a, b$ not divisible by $p$. Let $\mathcal{C}$ be the set of sequences $(x_n)$ of rational numbers that are Cauchy with respect to $|\cdot|_p$. With termwise addition and multiplication, $\mathcal{C}$ is a commutative ring with identity. Let $\mathcal{N} \subseteq \mathcal{C}$ be the set of null sequences, those with $|x_n|_p \to 0$; it is a maximal ideal of $\mathcal{C}$. The *field of $p$-adic numbers* is the quotient field $\mathbb{Q}_p = \mathcal{C}/\mathcal{N}$, whose elements are the classes of Cauchy sequences under the relation that two sequences are equivalent when their difference is a null sequence. The field $\mathbb{Q}$ is regarded as a subfield of $\mathbb{Q}_p$ through the injective ring homomorphism sending $a \in \mathbb{Q}$ to the class of the constant sequence $(a, a, a, \dots)$.

## Sources

- Fernando Q. Gouvêa, p-adic Numbers: An Introduction, 3rd ed., Universitext, Springer, 2020.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the $p$-adic absolute value on the rational numbers: `padicNorm`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Padics/PadicNorm.lean#L44-L47.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Cauchy completion as Cauchy sequences up to null differences: `CauSeq.Completion.Cauchy`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Order/CauSeq/Completion.lean#L33-L36.
