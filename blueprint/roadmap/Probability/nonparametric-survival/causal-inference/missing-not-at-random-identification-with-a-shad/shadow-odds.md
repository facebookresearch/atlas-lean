# Shadow Odds

Let $\mathcal{Y}$ be a set, $\mathcal{Z}$ a finite set, and $P$ a measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ with coordinates $R$, $Y$, $Z$; write $p(r, y, z) = P(\{(r, y, z)\})$ as a real number (an infinite point mass counts as $0$). The nonresponse odds at the outcome value $y$ are

$$a(y) = \frac{\sum_{z \in \mathcal{Z}} p(\mathrm{false}, y, z)}{\sum_{z \in \mathcal{Z}} p(\mathrm{true}, y, z)},$$

with the convention $x / 0 = 0$. For a finite measure with measurable singletons, this is $P(R = \mathrm{false}, Y = y) / P(R = \mathrm{true}, Y = y)$.
