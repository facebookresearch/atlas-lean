# Overall survival just before an observation time

In grouped competing-risks data, the overall Kaplan–Meier survival just before $t_j$, blind to the
causes, is

$$\hat S(t_j^-) = \prod_{l < j} \Bigl(1 - \frac{d_l}{Y_l}\Bigr),$$

where $d_l$ counts the failures from any cause at $t_l$ and a ratio with denominator $0$ is taken to be
$0$.
