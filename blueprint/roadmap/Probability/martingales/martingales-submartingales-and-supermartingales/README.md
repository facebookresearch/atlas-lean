# Martingales, submartingales and supermartingales

Given a filtration $(\mathcal F_n)$, an increasing sequence of σ-fields, an adapted sequence of integrable random
variables $X_n$ is a martingale if $E(X_{n+1} \mid \mathcal F_n) = X_n$ almost surely for every $n$, a submartingale if
$E(X_{n+1} \mid \mathcal F_n) \ge X_n$, and a supermartingale if $E(X_{n+1} \mid \mathcal F_n) \le X_n$.

## Idea

A martingale models the fortune of a gambler in a fair game: given the past, the expected fortune after the next round
is the present one. If $\xi_1, \xi_2, \dots$ are independent with mean $0$ and $S_n = \xi_1 + \dots + \xi_n$, then
$(S_n)$ is a martingale for $\mathcal F_n = \sigma(\xi_1, \dots, \xi_n)$; with means $\le 0$ it is a supermartingale.
Expected values are constant along a martingale and nondecreasing along a submartingale. A predictable sequence, the
second statement of this card, is a betting strategy that may use the past but not the coming round. Betting a bounded
nonnegative predictable amount on each round of a submartingale gives a submartingale, the third statement; applied to
$-X$, it says that no such strategy turns a supermartingale, an unfavourable game, into a favourable one.

## Statements

- [Martingales, submartingales and supermartingales](martingale.md)
- [Predictable sequence](predictable-sequence.md): predictable sequences, the strategies of the gambling picture
- [Bounded nonnegative predictable transforms of a submartingale](sum-mul-sub.md): a basic fact: betting a bounded nonnegative predictable amount on a submartingale gives a submartingale

## Background

- [Conditional expectation given a σ-field](../../foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/README.md): conditional expectation
- [Expected value](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values
