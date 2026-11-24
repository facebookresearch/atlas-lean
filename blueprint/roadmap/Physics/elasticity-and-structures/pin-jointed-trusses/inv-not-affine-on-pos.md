# Inv not affine on pos

Scope guard for unknown stiffness: the one-degree-of-freedom
displacement at unit load as a function of a positive scalar
stiffness `s`, namely `s⁻¹`, is not affine (in particular not linear)
in `s`. A stiffness-parameter inverse problem therefore cannot reuse
the fixed-stiffness linear observation matrix; it needs a separate
nonlinear or local model. No varying-stiffness identifiability
statement is made here.
