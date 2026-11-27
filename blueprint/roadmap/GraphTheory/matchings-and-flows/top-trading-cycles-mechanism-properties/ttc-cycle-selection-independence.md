# Top trading cycles is independent of the cycle-selection order

In a Shapley-Scarf housing market with strict preferences, consider any rule that, while agents remain, selects a nonempty set of the current top-trading cycles (closed under following top choices), assigns each selected agent its pointed house and removes them. Every such rule produces the same allocation as removing all current cycles simultaneously in each round, namely the top trading cycles allocation; in particular selecting a single cycle per step gives the TTC allocation.

## Proof sketch

Removing one cycle does not change the top choices of agents on other current cycles, so the other cycles persist; induction on the number of agents.

## Depends on

- [Shapley-Scarf housing markets](../../../GameTheory/matching-markets/housing-markets/shapley-scarf-housing-markets.md)
- [Top trading cycles for housing markets](../../../GameTheory/matching-markets/housing-markets/top-trading-cycles-for-housing-markets.md)

## Sources

- L. Shapley and H. Scarf, "On Cores and Indivisibility", Journal of Mathematical Economics 1(1), 1974.
- J. Schummer and R. V. Vohra, "Mechanism Design without Money", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
- T. Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Cambridge University Press, 2016.
