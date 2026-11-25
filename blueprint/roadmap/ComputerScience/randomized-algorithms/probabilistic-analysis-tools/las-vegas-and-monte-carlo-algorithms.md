# Las Vegas and Monte Carlo algorithms

A *randomized algorithm* is an algorithm, for example a Turing machine or a random-access machine, that may also flip independent fair coins. On a fixed input, its output and its running time are random variables.
- A *Las Vegas* algorithm always outputs a correct answer. Its running time is random, with finite expectation on every input.
- A *Monte Carlo* algorithm has a bounded running time, but may output a wrong answer. For a decision problem, the error is classified as follows.
    - *One-sided error:* on no-instances the algorithm always answers no, and on yes-instances it answers yes with probability at least a constant $p > 0$, or the same with yes and no exchanged. Polynomial-time algorithms of the first kind define the class RP, and those of the second kind define coRP.
    - *Two-sided error:* on every input it answers correctly with probability at least $1/2 + \varepsilon$ for a constant $\varepsilon > 0$. Polynomial-time algorithms of this kind define the class BPP.

**Facts.**
1. A Las Vegas algorithm with expected running time $T(x)$ becomes a Monte Carlo algorithm with running time at most $c\,T(x)$: stop after $c\,T(x)$ steps and output an arbitrary answer. By Markov's inequality, this errs with probability at most $1/c$. The error is one-sided if the default answer is chosen suitably.
2. A Monte Carlo algorithm with running time $T$ and success probability $q > 0$, whose answers can be checked by a verifier in time $V$, becomes a Las Vegas algorithm with expected running time $(T + V)/q$: repeat until the verifier accepts.
3. *Amplification.* Repeating a one-sided-error algorithm $t$ times lowers its error to $(1 - p)^t \le e^{-pt}$. For two-sided error, the majority answer of $t$ runs errs with probability at most $e^{-2\varepsilon^2 t}$.

**Proof.**
1. The truncated run errs only if the running time exceeds $c\,T(x)$.
2. Each round succeeds independently with probability at least $q$, so the number of rounds is geometric with mean at most $1/q$.
3. The independent runs all fail with probability $(1 - p)^t$. For the majority vote, use a Chernoff bound.

## Background

- [Error amplification by independent repetition](error-amplification-by-independent-repetition.md)

## Sources

- G. Valiant and M. Wootters, *CS265/CME309: Randomized Algorithms and Probabilistic Analysis*, Lecture 1 "Computational models, and the Schwartz–Zippel randomized polynomial identity test", Stanford University, <https://web.stanford.edu/class/archive/cs/cs265/cs265.1224/Lectures/Lecture1/l1.pdf>, Section 2: Definition 2.1 (randomized algorithms as machines with random bits), the Las Vegas and Monte Carlo classes (Las Vegas: always correct with finite expected running time; Monte Carlo: bounded running time with one-sided error $p > 0$ or two-sided error $1/2 + \varepsilon$; the classes RP and BPP), amplification with $(1 - p)^t \le e^{-pt}$, Lemma 2.2 (the majority of $t$ runs is correct with probability at least $1 - e^{-2\varepsilon^2 t}$), and Question 1 on converting between the two classes. The conversions are proved here.
