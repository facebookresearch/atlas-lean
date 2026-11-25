# Bounded polygonal workspace

A bounded polygonal workspace in the Euclidean plane consists of

- an outer simple polygon with region $R_0$;
- a finite list of hole simple polygons with regions $R_1, \dots, R_m$;

subject to the conditions

- every hole closure lies in the interior of the outer region: $\overline{R_i} \subseteq \operatorname{int}(R_0)$ for $1 \le i \le m$;
- the closures of holes at distinct positions of the list are disjoint: $\overline{R_i} \cap \overline{R_j} = \emptyset$ for $1 \le i < j \le m$.
