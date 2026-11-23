# Patterson Aux1 one

Patterson's Equation A6: `a₁(1) = 1`. At `x = 1` the Lean computation uses
`(1 - x) * log (1 - x) = 0 * log 0 = 0`; `tendsto_pattersonAux1_nhdsLT_one` shows
the value is also the limit from below.
