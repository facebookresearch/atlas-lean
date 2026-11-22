# If s + f > 0, flow balance fixes the steady-state unemployment rate

The labour force is
normalized to `1`, so employment is `1 - u` and unemployment is `u`. In each period a
fraction `s` of the employed separate and a fraction `f` of the unemployed find jobs.
Steady state means flows balance: `s * (1 - u) = f * u`. When `s + f > 0`, the unique
steady-state unemployment rate is `u = s / (s + f)`. No labour-force growth, entry, or
exit is modelled. The calculation needs neither nonnegativity nor an upper bound on `s`
and `f`. The case `s = f = 0` is excluded: with no flows every `u` is steady.
