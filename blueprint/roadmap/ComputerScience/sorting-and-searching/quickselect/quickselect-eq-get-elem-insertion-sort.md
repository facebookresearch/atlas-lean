# Quickselect agrees with sorting

Let $L$ be a list over a linear order, let $S$ be the
insertion sort of $L$ in nondecreasing order, and let $k$ be a natural number. If $k < |L|$,
quickselect on $L$ with zero-based rank $k$ returns the entry of $S$ at zero-based position $k$;
if $k \ge |L|$, it returns no element.
