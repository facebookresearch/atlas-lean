# Positively unate variable

Let $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ be a Boolean function and $i$ one of its $n$ variables. Then
$f$ is positively unate in $i$ if for all assignments $x$ and $y$ that agree at every variable
other than $i$ and have $x_i = \mathrm{false}$ and $y_i = \mathrm{true}$, $f(x) = \mathrm{true}$
implies $f(y) = \mathrm{true}$. Equivalently, switching $i$ from false to true never switches
the value of $f$ from true to false.

## Sources

- [OWR-10252930-018], unate.
