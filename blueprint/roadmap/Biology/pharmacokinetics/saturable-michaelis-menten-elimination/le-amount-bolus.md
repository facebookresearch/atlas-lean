# Upper barrier after a bolus

Since `C ≤ C₀`, elimination is at least first order with
the slowest rate `Vmax / (Km + C₀)`: `C(t) ≤ C₀ e^{-(Vmax / (Km + C₀)) t}`. Together with
`IsSolution.amount_le` this brackets the bolus curve between two linear washouts.
