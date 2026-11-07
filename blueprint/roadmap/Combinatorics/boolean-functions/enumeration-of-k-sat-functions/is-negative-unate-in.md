# Negatively unate variable

Let $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ be a Boolean function and $i$ one of its $n$ variables. Then
$f$ is negatively unate in $i$ if for all assignments $x$ and $y$ that agree at every variable
other than $i$ and have $x_i = \mathrm{false}$ and $y_i = \mathrm{true}$, $f(y) = \mathrm{true}$
implies $f(x) = \mathrm{true}$. Equivalently, switching $i$ from false to true never switches
the value of $f$ from false to true.

## Sources

- [OWR-10252930-018], unate.
