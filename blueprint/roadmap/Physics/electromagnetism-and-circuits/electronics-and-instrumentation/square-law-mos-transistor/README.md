# Square-law MOS transistor

## The piecewise drain-current model

- [Triode-region drain-current formula of the square-law MOS model](triode-current.md)
- [Saturation-region drain-current formula of the square-law MOS model](saturation-current.md)
- [Piecewise square-law drain current with cutoff, triode and saturation](current.md)

## Region formulas

- [With nonpositive overdrive the drain current is zero (cutoff)](current-of-nonpos.md)
- [With $u > 0$ and $0 \le V_{DS} \le u$ the current is the triode value](current-of-triode.md)
- [For positive overdrive and $V_{DS} \ge u$ the saturation formula holds](current-of-saturation.md)
- [The triode and saturation formulas agree at $V_{DS} = u$](triode-eq-saturation-at-boundary.md)
- [For positive overdrive the current at $V_{DS} = u$ is the common value](current-at-boundary.md)

## Continuity at the region boundaries

- [For $V_{DS} \ge 0$ the current is continuous in $u$ at the threshold](continuous-at-u-zero.md)
- [For $u > 0$ the current is continuous in $V_{DS}$ at $V_{DS} = u$](continuous-at-vds-boundary.md)
- [For $V_{DS} > 0$ the current is continuous in $u$ at $u = V_{DS}$](continuous-at-u-boundary.md)
- [For positive overdrive the current is jointly continuous at $(u, u)$](continuous-at-joint-boundary.md)

## Transconductance and output conductance

- [Below threshold the transconductance is zero](has-deriv-at-u-cutoff.md)
- [Below threshold the output conductance is zero](has-deriv-at-vds-cutoff.md)
- [Inside the triode region the transconductance is $\beta V_{DS}$](has-deriv-at-u-triode.md)
- [Inside the triode region the output conductance is $\beta(u - V_{DS})$](has-deriv-at-vds-triode.md)
- [Inside the saturation region the transconductance is $\beta u$](has-deriv-at-u-saturation.md)
- [Inside the saturation region the output conductance is zero](has-deriv-at-vds-saturation.md)
- [For $\beta > 0$ and $V_{DS} \le u$, $\beta(u - V_{DS})$ is nonnegative](triode-gds-nonneg.md)

## Sign of the current and the bundled model

- [For $\beta > 0$ and $V_{DS} \ge 0$ the drain current is nonnegative](current-nonneg.md)
- [Properties of the ideal square-law MOS model for $\beta > 0$](ideal-square-law-mos-spec.md)
