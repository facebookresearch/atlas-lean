# Species balance: inflow minus outflow plus generation is accumulation

For an inlet [process stream](stream-flow.md) with species flow rates `ṅ_in i`, an outlet stream
with species flow rates `ṅ_out i` over the same finite species type, and real vectors `gen` (net
generation rates) and `acc` (accumulation rates), the species balance holds when

`ṅ_in i - ṅ_out i + gen i = acc i` for every species `i`.

The stream flows are nonnegative, while `gen` and `acc` may have either sign: net consumption is a
negative `gen i`, and depletion a negative `acc i`. All four terms are read as rates in one
consistent set of units. The balance has exactly one inlet and one outlet stream.
