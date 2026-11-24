# Robustly Feasible

Robust feasibility (MIT 16.410): a solution whose delta-thickening stays free.

The witness `γ` is a solution (as in LaValle, Planning Algorithms, Ch. 4.3.1
Formulation 4.1), and for some radius `δ > 0` the `δ`-thickening of its range stays
inside the free set, i.e. the solution survives dilating the obstacles by `δ` (MIT
"robust solution").
