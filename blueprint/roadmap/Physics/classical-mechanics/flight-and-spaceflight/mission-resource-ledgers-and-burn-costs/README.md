# Mission resource ledgers and burn costs

## Resource stocks and schedules

- [Stock of a resource after the first t steps](stock.md)
- [Gains of a resource at a step](gains.md)
- [Draws of a resource at a step](draws.md)
- [Prefix feasibility of a resource schedule](prefix-feasible.md)
- [Flow schedule given by a finite list](list-flow.md)

## Prefix stocks

- [Before any step the stock is the initial stock](stock-zero.md)
- [Each step adds its signed flow to the stock](stock-succ.md)

## Prefix bounds and the reserve

- [Prefix feasibility includes the terminal check](terminal.md)
- [A prefix-feasible schedule never takes a stock below its floor up to N](lo-le-stock.md)
- [A reserve in the floor is one deduction from the initial stock](prefix-feasible-iff-reserve-deducted-onc.md)
- [Deducting the reserve at every step removes it t times](stock-reserve-every-step.md)

## Burn cost and net velocity change

- [Delta-v cost of a sequence of burns](burn-cost.md)
- [Net velocity change of a sequence of burns](net-velocity-change.md)
- [The delta-v cost is nonnegative](burn-cost-nonneg.md)
- [The net velocity change is at most the delta-v cost](norm-net-velocity-change-le-burn-cost.md)
- [Two opposite equal burns cost twice the magnitude with zero net change](opposite-burns.md)

## Burn cost from stage masses

- [Admissible stage masses of a sequence of burns](admissible-stage-masses.md)
- [Ideal velocity increment of a burn](stage-increment.md)
- [At positive exhaust speed admissible burns have nonnegative increments](stage-increment-nonneg.md)
- [A depleted or negative stage mass is not admissible](stage-masses-rejects-depleted.md)
- [Delta-v cost of staged burns from their stage masses](burn-cost-staged.md)
- [For collinear staged burns the net change has the norm of the cost](net-velocity-change-staged-collinear.md)

## Fuel consumption

- [Remaining mass fractions of burns at one exhaust speed multiply](remaining-fraction-burns.md)
- [Fuel consumption follows the delta-v cost, not the net change](fuel-burn-cost.md)
- [Remaining mass fraction of admissible staged burns](stage-remaining-fraction.md)
