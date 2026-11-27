# Linear programs are solvable in polynomial time

There is an algorithm that, given a linear program $\min\{c^\top x : A x = b,\ x \ge 0\}$ in standard equality form with rational data, decides whether it is feasible and whether it is bounded and, if it has an optimum, returns an optimal vertex of its feasible region (which, lying in the nonnegative orthant, has vertices whenever it is nonempty), in time polynomial in the [encoding size](encoding-size-of-a-linear-program.md) of the input. The feasibility part is [linear programming is in P](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md); this page adds optimization, which lexicographic ranking and PCTL model checking use. The first such algorithm was Khachiyan's ellipsoid method (1979); interior-point methods, starting with Karmarkar's algorithm (1984), give others, for example Ye's potential-reduction algorithm with $O(\sqrt{n}\,L)$ iterations.

## Expansion

This page becomes ready once these prerequisites are stated:

- The potential function of Ye's interior-point algorithm and the constant decrease per primal or dual step that gives $O(\sqrt{n}\, L)$ iterations (proof prerequisite)
- The bound on the bit size of the numbers in Gaussian elimination (Theorem 27 of the notes) used to keep each iteration polynomial (proof prerequisite)

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Linear programming is in P (Khachiyan)](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md)
- [The measure L exceeds the encoding size by at most a constant](the-measure-l-is-at-most-the-encoding-size.md)
- [Near-optimal points round to optimal vertices](near-optimal-points-round-to-optimal-vertices.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 13 (polynomial-time algorithms: Khachiyan's ellipsoid method and interior-point methods), Section 13.1 (the potential function and Lemma 21), Sections 14–15 (Ye's interior-point algorithm and its analysis) and Section 16 (bit complexity, Theorem 27).
