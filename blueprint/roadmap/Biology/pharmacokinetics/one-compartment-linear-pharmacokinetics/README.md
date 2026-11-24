# One-compartment linear pharmacokinetics

## Model and mass balance

- [Elimination rate constant](elim-rate.md)
- [Concentration in the one-compartment model](concentration.md)
- [Mass balance of the linear one-compartment model](add-integral-eq.md)
- [Mass balance of the explicit amount](amount-add-eliminated.md)

## Bolus: concentration and area under the curve

- [Concentration after a bolus](concentration-bolus.md)
- [Finite-horizon AUC](integral-concentration-bolus.md)
- [For CL > 0 the bolus concentration is integrable on the half-line](integrable-on-concentration-bolus.md)
- [Total AUC after a bolus is the dose over the clearance](integral-ici-concentration-bolus.md)
- [The finite-horizon AUC tends to the total AUC](tendsto-integral-concentration-bolus.md)
- [Half-life in terms of clearance and volume](half-life-elim-rate.md)

## Constant infusion and boundary cases

- [For CL > 0, under constant infusion the concentration tends to R / CL](tendsto-concentration.md)
- [Starting at or below the steady state the amount is nondecreasing](amount-monotone.md)
- [With no elimination and no input the amount is constant](amount-rate-zero-input-zero.md)
- [Without elimination a positive input makes the amount unbounded](tendsto-amount-rate-zero-at-top.md)
- [Without elimination a positive input gives no finite limit](not-tendsto-amount-rate-zero.md)
- [Without elimination a nonzero input has no constant solution](not-is-solution-const-rate-zero.md)
- [For k > 0 the amount after a bolus washes out to zero](tendsto-amount-bolus.md)

## Identifying the parameters from bolus observations

- [Absolute bolus reconstruction](bolus-absolute-reconstruction.md)
- [Two exact bolus observations determine volume and clearance](bolus-absolute-injective.md)
- [Normalized washout identifies the elimination rate](normalized-washout-rate.md)
- [Scaling obstruction for separate parameters](normalized-scaling-same-washout.md)

## Repeated dosing

- [Finite-horizon dose budget](dose-budget-from-integral-equation.md)
- [Amount just after the n-th dose of a periodic schedule](post-dose-amount.md)
- [Decay between events](periodic-amount-decay.md)
- [At a dose time the trajectory equals the post-dose amount](post-dose-amount-at-event.md)
- [Post-dose amounts satisfy the affine recurrence](post-dose-amount-succ.md)
- [Without elimination the post-dose amount is n + 1 doses](post-dose-amount-zero-elimination.md)
- [Post-dose closed form for the periodic trajectory](post-dose-amount-closed-form.md)
- [Steady-state post-dose limit](post-dose-tendsto.md)
- [Steady-state trough](trough-tendsto.md)
