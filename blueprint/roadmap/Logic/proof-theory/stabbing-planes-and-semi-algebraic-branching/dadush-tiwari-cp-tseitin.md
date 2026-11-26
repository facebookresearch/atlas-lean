# Dadush–Tiwari: cutting planes refute Tseitin formulas in quasi-polynomial size

For every bounded-degree graph $H$ on $n$ vertices and every odd charge function, the Tseitin formula of $H$ has cutting planes refutations of size $2^{O(\log^2 n)}$ (quasi-polynomial), refuting the conjecture that Tseitin formulas on expanders require exponential cutting planes size. More generally, stabbing planes refutations with coefficients of quasi-polynomially bounded magnitude can be converted into cutting planes refutations with quasi-polynomial blow-up (Fleming et al.).

## Proof sketch

Simulate the stabbing planes recursion for Tseitin inside cutting planes: each branch on a bounded-coefficient inequality is replaced by a cutting planes derivation that handles all integer values of the queried form at once, using the fact that a disjunction of polynomially many parallel slabs can be eliminated by a sequence of Chvátal-Gomory cuts with small coefficients. The bounded number of possible values of each query keeps the overall blow-up quasi-polynomial.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)

## Proof depends on

- [Stabbing planes refute Tseitin formulas in quasi-polynomial size](sp-tseitin-quasipoly.md)
- [Stabbing planes simulate cutting planes and equal tree-like R(CP)](sp-simulates-cutting-planes.md)

## Sources

- D. Dadush, S. Tiwari, "On the complexity of branching proofs", CCC (2020), arXiv:2006.04124.
- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", CCC (2021), arXiv:2102.05019.
