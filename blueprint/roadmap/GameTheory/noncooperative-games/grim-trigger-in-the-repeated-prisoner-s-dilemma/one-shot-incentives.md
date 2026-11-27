# One Shot Incentives

The one-shot incentive inequalities of grim trigger with discount factor `δ`, for every real `δ`: for every state `s` and every action `a'`,

$$(1 - \delta)\,\mathrm{stage}(a', \mathrm{action}(s)) + \delta\, V(\mathrm{next}(s, a', \mathrm{action}(s))) \le V(s),$$

where `action(s)` is the [action](action.md) grim trigger prescribes in state `s`, `next` is its [transition](next.md), `stage` is the [stage payoff](stage.md) and `V` its normalized [value](value.md). At `δ = 0` only the current stage counts and at `δ = 1` only the continuation. For `0 ≤ δ < 1` the inequality says that no single-period deviation to `a'` against the prescribed action of the opponent, followed by a return to grim trigger from the resulting state, gives a higher normalized discounted value.
