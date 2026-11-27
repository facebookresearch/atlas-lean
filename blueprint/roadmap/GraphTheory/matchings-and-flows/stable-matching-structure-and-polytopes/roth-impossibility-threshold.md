# Roth's impossibility for every market size n >= 3, and possibility for n <= 2

For every $n \ge 3$ there is no matching mechanism on markets with $n$ proposers and $n$ receivers and strict complete preferences that is stable and strategy-proof for all agents. For $n \le 2$, proposer-proposing deferred acceptance is strategy-proof also for the receivers (and receiver-proposing deferred acceptance for the proposers), so a stable mechanism that is strategy-proof for all agents exists; the threshold $n = 3$ is sharp.

## Proof sketch

Pad Roth's three-by-three market with $n - 3$ mutually top-ranked dummy pairs, which every stable matching must match together; a manipulation in the small market lifts. For $n \le 2$ check the finitely many preference profiles.

## Depends on

- [Stable matching mechanism](../../../GameTheory/matching-markets/stable-matching-mechanisms-and-incentives/is-stable-mechanism.md)
- [Strategy-proof matching mechanism](../../../GameTheory/matching-markets/stable-matching-mechanisms-and-incentives/is-strategy-proof.md)

## Proof depends on

- [Roth's impossibility theorem](../../../GameTheory/matching-markets/stable-matching-mechanisms-and-incentives/not-exists-stable-strategy-proof.md)

## Sources

- A. E. Roth, "The Economics of Matching: Stability and Incentives", Mathematics of Operations Research 7(4), 1982.
- J. Schummer and R. V. Vohra, "Mechanism Design without Money", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
