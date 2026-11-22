# Positive reactor volume

A reactor volume: a real number `V > 0`. The extent-rate convention divides by `V`, so the
positivity is part of the type. With `V = 0` Lean's division would turn every extent trajectory
into a zero rate and a constant concentration instead of an undefined model.
