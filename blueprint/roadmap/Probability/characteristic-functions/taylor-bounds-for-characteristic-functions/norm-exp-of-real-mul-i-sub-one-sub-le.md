# Global second-order bound for the imaginary exponential

For every real number $u$,
$|e^{iu} - 1 - iu| \le u^2$, with no restriction on the size of $u$.

The proof splits at $u^2 \le 27$: in that range the squared norm is
$(1 - \cos u)^2 + (u - \sin u)^2 \le u^4/4 + u^6/36 \le u^4$, using $1 - \cos u \le u^2/2$ and
$|u - \sin u| \le |u|^3/6$; outside that range $|u| > 5$ and the triangle inequality gives
$2 + |u| \le u^2$.
