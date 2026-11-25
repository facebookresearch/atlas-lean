# Admissible pair for the key renewal theorem

`KeyRenewalAdmissible Y y`
says that the input `y` and the candidate solution `Y` lie in the class where
the key renewal theorem (Feller Vol. II, §XI.1, Theorem 2, with uniqueness from
§XI.1, Theorem 1) applies:

* `y` is measurable, vanishes on `(-∞, 0)`, is continuous at almost every point,
  and on `[0, ∞)` is dominated in absolute value by an antitone majorant that is
  integrable on `[0, ∞)`; this is the standard sufficient condition for direct
  Riemann integrability (Feller §XI.1, condition (b); Asmussen, *Applied
  Probability and Queues*, Prop. V.4.1);
* `Y` is measurable, vanishes on `(-∞, 0)` and is bounded on every half-line
  `(-∞, T]`, so it is the unique such solution of its renewal equation.

This is a sufficient condition, not a definition of direct Riemann
integrability.
