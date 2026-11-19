# LogDet (paralinear) distance

For a real square matrix $F$ indexed by a finite set (a joint distribution matrix $F_{ij} = \Pr(X = i, Y = j)$), the LogDet distance is

$$d_{LD}(F) = -\log|\det F| + \frac12\Bigl(\log \prod_i \sum_j F_{ij} + \log \prod_j \sum_i F_{ij}\Bigr),$$

with the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. It is a distance when $\det F \ne 0$ and the marginals are positive.
