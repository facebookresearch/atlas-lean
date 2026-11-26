# Enzyme sharing enables oscillations in transformation cycles

**Setting.** A *transformation cycle* is the substrate hypergraph cycle $X_1\to X_2\to\cdots\to X_n\to X_1$ in which each reaction converts one substrate into the next. Each reaction $X_i\to X_{i+1}$ is realized by a Henri-Michaelis-Menten module $E+X_i\rightleftarrows C_i\to E+X_{i+1}$ under mass action, where the catalyzing enzyme $E$ is chosen by an enzyme assignment: distinct enzymes, an enzyme shared among several reactions, or no enzyme (a direct reaction $X_i\rightleftarrows C_i\to X_{i+1}$). For every assignment, each positive stoichiometric compatibility class has a unique positive steady state.

**Theorem 1.3 (the smallest oscillating transformation cycle).** For the three-substrate cycle $X_1\to X_2\to X_3\to X_1$ in which one enzyme catalyzes two reactions and the third reaction is catalyzed by a second enzyme or is enzyme-free:
1. there exist positive rate constants and a positive compatibility class whose unique positive steady state is unstable;
2. along a one-parameter family of rate constants this steady state undergoes a supercritical Hopf bifurcation, producing a limit cycle that is orbitally asymptotically stable within the class;
3. among transformation cycles with at most three reactions and any enzyme assignment (enzyme-free reactions allowed), some rate constants and some positive class admit a trajectory that does not converge to the positive steady state if and only if the cycle has three reactions and some enzyme catalyzes exactly two of them.

**Proposition 7.4 (one enzyme on every reaction).** If a single enzyme catalyzes all $n\ge1$ reactions of a transformation cycle, every trajectory in a positive compatibility class converges to its positive steady state, for all positive rate constants.

## Expansion

When each enzyme serves one reaction, or one enzyme serves all of them, the dynamics are monotone in suitable reaction coordinates and converge. Sharing one enzyme between exactly two of three reactions couples those two modules through competition for free enzyme, which breaks monotonicity. The explicit instance in Proposition 7.1 has a steady state whose Jacobian, restricted to the compatibility class, has a pair of eigenvalues with positive real part; Proposition 7.2 moves one binding constant $s$ through a critical value where that pair crosses the imaginary axis transversally with negative first Lyapunov coefficient, which is the supercritical Hopf condition. Proposition 7.5 rules out non-convergence for every other assignment pattern on at most three reactions, which gives the "if and only if" in part 3.

## Sources

- B. Joshi, T. D. Nguyen, "Substrate hypergraph cycles: unique steady states and persistence for every enzyme assignment; oscillations enabled by enzyme sharing", arXiv preprint (2026), Theorem 1.3, Propositions 7.1-7.5, <https://doi.org/10.48550/arXiv.2611.02523>.
