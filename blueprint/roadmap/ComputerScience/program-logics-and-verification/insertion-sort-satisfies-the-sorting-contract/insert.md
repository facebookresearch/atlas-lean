# Ordered insertion into a list

For a linearly ordered type $\alpha$, inserting $x$ into a list $xs$ places $x$ before the first element $y$ with $x \le y$ (at the end if there is none), keeping duplicates:

$$\mathrm{insert}(x, []) = [x], \qquad \mathrm{insert}(x, y :: ys) = \begin{cases} x :: y :: ys & x \le y, \\ y :: \mathrm{insert}(x, ys) & \text{otherwise.} \end{cases}$$

It is the standard ordered insertion of lists under $\le$.
