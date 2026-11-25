# Path-side and edge-side total travel time agree

Let finitely many routes $p$ carry flows $f_p$, each route a list of arcs (repetition allowed), and let the arc volume be $x_e = \sum_p f_p\,(\text{number of times route } p \text{ uses } e)$. For any arc travel-time functions $t_e$,

$$\sum_p f_p\sum_{e \in p} t_e(x_e) = \sum_e x_e\,t_e(x_e),$$

where the inner sum counts repeated arcs with multiplicity.
