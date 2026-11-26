# Random CNFs are hard for cutting planes

For $k = C\log n$ with a sufficiently large constant $C$ and a suitable polynomial number $m$ of clauses, a random $k$-CNF formula on $n$ variables is unsatisfiable and with high probability requires cutting planes refutations of size $2^{n^{\Omega(1)}}$ (Fleming-Pankratov-Pitassi-Robere; independently Hrubeš-Pudlák for random $k$-CNFs with $k$ a sufficiently large constant, via a monotone-real-circuit interpolation argument). These were the first cutting planes lower bounds for random formulas.

## Proof sketch

Show that random CNFs, under a random partition of variables, contain a hard instance of a communication search problem that has no small real (dag-like) communication protocol: Hrubeš-Pudlák use a monotone real circuit lower bound for a random-graph-based monotone function obtained by interpolation, while Fleming et al. prove a lower bound for real communication protocols via a lifting argument with random gadgets embedded in the random formula.

## Proof depends on

- [Haken–Cook / Pudlák: exponential lower bounds for monotone real circuits](haken-cook-monotone-real.md)
- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Sources

- N. Fleming, D. Pankratov, T. Pitassi, R. Robere, "Random Theta(log n)-CNFs are hard for cutting planes", FOCS (2017); Journal of the ACM 69 (2022).
- P. Hrubeš, P. Pudlák, "Random formulas, monotone circuits, and interpolation", FOCS (2017).
