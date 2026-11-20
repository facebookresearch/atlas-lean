# Derivative of a packed SIR curve

The packed curve $(S, I, R)$ has derivative $F(S(t), I(t), R(t))$ at $t$, where $F$ is the SIR vector
field, if and only if the three SIR equations hold at $t$ with two-sided derivatives:
$$S'(t) = -\frac{\beta S(t) I(t)}{N}, \quad I'(t) = \frac{\beta S(t) I(t)}{N} - \gamma I(t), \quad R'(t) = \gamma I(t).$$
