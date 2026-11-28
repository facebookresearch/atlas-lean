# Semistable Weil Deligne

Weil–Deligne structure of semistable cohomology: let $ℓ$ be a prime, $R$ a henselian discrete
valuation ring whose residue field has characteristic $p ≠ ℓ$, $K$ its fraction field, $L$ an
algebraic closure of $K$, $π ∈ R$ with geometric-trait data $T$ (`GeometricTrait`), $X$ a proper
$R$-scheme that is strictly semistable with respect to $π$, and $n ∈ ℕ$. Assume that the Galois
operators on the rational $ℓ$-adic cohomology $H^n$ of $X_L$ form an action
(`CohomologyFunctoriality`), and fix an arithmetic Frobenius $A$ (`ArithmeticFrobenius`, which
includes finiteness of the residue field) and a tame coordinate $B$ (`TameCoordinate`). Then, for
$N$ the logarithm of the operator of the tame generator: $N^{n+1} = 0$, every inertia element $σ$
acts by $\exp(t_B(σ) N)$, and $ρ(w) N = q^{\deg w} N ρ(w)$ for every $w$ in the Weil group, where
$ρ(w)$ is the Frobenius operator to the power $\deg w$ and $q$ is the cardinality of the residue
field (`SemistableWeilDeligneLaws`).
