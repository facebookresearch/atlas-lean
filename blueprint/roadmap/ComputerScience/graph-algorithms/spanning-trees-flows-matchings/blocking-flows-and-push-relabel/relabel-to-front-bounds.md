# Relabel-to-front performs O(|V|^3) operations

The **relabel-to-front** scheduler keeps the vertices other than $s, t$ in a list, discharges the current vertex (pushing along admissible arcs found by a current-arc pointer into its neighbour list, relabelling when the pointer runs out), and moves a vertex to the front of the list whenever its discharge relabels it. With valid neighbour lists it performs a valid run of push and relabel operations ending in a maximum flow and a minimum cut of equal value, with at most $2|V|^2$ relabels, $2|V||E|$ saturating pushes, $(|V| - 2)\big((|V| - 2)(2|V| - 1) + 1\big)$ discharge calls, at most as many nonsaturating pushes as discharges, at most $4|V|^3$ push and relabel operations in total, and at most $2|V| \sum_v \deg(v)$ current-arc advances.

## Proof sketch

The list is a topological order of the admissible network; a full pass without relabels empties all excess, so between consecutive relabels there are at most $|V|$ discharges, each with at most one nonsaturating push.

## Depends on

- [Preflows, valid labelings, push and relabel](preflows-and-valid-labelings.md)

## Proof depends on

- [Operation bounds for generic push-relabel](push-relabel-operation-bounds.md)

## Sources

- A. V. Goldberg and R. E. Tarjan, "A New Approach to the Maximum-Flow Problem", Journal of the ACM 35(4), 1988.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
