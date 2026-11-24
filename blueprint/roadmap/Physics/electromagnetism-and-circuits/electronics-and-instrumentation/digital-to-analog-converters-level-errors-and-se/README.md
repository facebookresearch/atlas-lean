# Digital-to-analog converters: level errors and settling

## Level errors

- [Actual output level of a DAC with level errors](dac-level.md)
- [The level error is the actual level minus the ideal level](dac-level-sub-mul.md)
- [Adjacent DAC steps are within $2\eta$ of the ideal step](abs-dac-level-add-one-sub-sub-le.md)
- [For $2\eta < \Delta$, the DAC levels are strictly increasing](dac-level-strict-mono-on.md)
- [The unclipped ADC-to-DAC error is at most $\Delta/2 + \eta$](abs-dac-level-code-sub-le-of-not-is-clip.md)
- [Full-scale inputs have ADC-to-DAC error at most $\Delta/2 + \eta$](abs-dac-level-code-sub-le-of-mem-icc.md)
- [The signed $w$-bit ADC-to-DAC error is at most $\Delta/2 + \eta$](abs-dac-level-code-signed-sub-le-of-not.md)
- [Step, monotonicity and ADC-to-DAC error bounds for a DAC](dac-level-correct.md)
- [For $2\eta < \Delta$, signed wraparound at full scale lowers the level](dac-level-to-int-int-max-add-one-lt.md)
- [For $\Delta \le 2\eta$, level errors can break strict monotonicity](exists-not-strict-mono-on-of-le-two-mul.md)

## Settling on a holding interval

- [Settling output of a first-order stage holding a level](settling-output.md)
- [The settling output starts at its initial value](settling-output-at-start.md)
- [On a holding interval, the output is the explicit settling output](held-output-eq-settling-output.md)
- [Output at the end of a holding interval](held-output-endpoint-recurrence.md)
- [The settling error is the initial mismatch times $e^{-(t - t_0)/\tau}$](settling-error-eq.md)
- [The settling error never exceeds the initial mismatch](settling-error-le-initial.md)
- [Settling across a change of held level at a junction](held-output-two-intervals.md)
- [Settling error against the actual level of a held code](code-held-settling-error-eq.md)
- [Settling on a holding interval: formula, endpoint value and error law](settling-correct.md)
