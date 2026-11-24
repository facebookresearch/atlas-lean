# Saturable Michaelis–Menten elimination

- [Saturable-elimination equation under constant infusion](is-solution.md)
- [Steady-state concentration under constant infusion](steady-conc.md)
- [Closed-form bolus AUC](bolus-auc.md)

## The elimination rate

- [Elimination is nonnegative at nonnegative concentrations](mm-rate-nonneg.md)
- [Michaelis–Menten elimination never exceeds Vmax](mm-rate-le.md)
- [Michaelis–Menten elimination is at most first order](mm-rate-le-mul.md)
- [On a bounded range elimination is at least first order](mul-le-mm-rate.md)
- [The infusion-minus-elimination field in deviation form](sub-mm-rate-eq.md)

## Existence, uniqueness, positivity

- [Solutions starting nonnegative stay nonnegative](nonneg.md)
- [Existence of a nonnegative solution](exists-is-solution.md)
- [Two solutions with the same nonnegative start agree](eq-of-initial.md)
- [Solutions starting positive stay positive](pos.md)

## Bounds and mass balance

- [Linear lower barrier](amount-le.md)
- [The concentration never exceeds the elimination-free accumulation](le-add-mul.md)
- [Zero-order lower bound](add-mul-le.md)
- [Mass balance under saturable elimination](add-integral-eq.md)

## Bolus: washout

- [After a bolus the concentration is nonincreasing](antitone-on-bolus.md)
- [Upper barrier after a bolus](le-amount-bolus.md)
- [After a bolus the concentration washes out to zero](tendsto-bolus.md)

## Bolus: area under the curve

- [Integrated balance after a bolus](integral-bolus.md)
- [The bolus AUC is finite](integrable-on-ioi-bolus.md)
- [Area under the bolus concentration curve](integral-ioi-bolus.md)

## Dose–AUC nonlinearity

- [AUC splits into a linear and a saturation part](bolus-auc-eq-integral-linear-add.md)
- [Doubling the dose more than doubles the bolus AUC](two-mul-bolus-auc-lt.md)
- [Bolus AUC per unit initial concentration](bolus-auc-div.md)
- [The bolus AUC per unit initial concentration is strictly increasing](strict-mono-on-bolus-auc-div.md)
- [AUC is not proportional to dose](not-exists-bolus-auc-eq-mul.md)
- [Low-dose limit](tendsto-bolus-auc-div.md)

## Constant infusion: steady state

- [A constant is a solution exactly when elimination balances infusion](is-solution-const-iff.md)
- [The steady-state concentration is nonnegative](steady-conc-nonneg.md)
- [Elimination at the steady-state concentration balances the infusion](mm-rate-steady-conc.md)
- [The steady-state concentration is a constant solution](is-solution-steady-conc.md)
- [Uniqueness of the steady state](eq-steady-conc-of-mm-rate-eq.md)
- [No steady state when infusion reaches capacity](not-is-solution-const-of-le.md)
- [Unbounded accumulation](tendsto-at-top.md)
- [Exponential approach to the steady state](abs-sub-steady-conc-le.md)
- [Convergence to the steady state](tendsto-steady-conc.md)
