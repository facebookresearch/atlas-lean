# Route certificates are supported on movements

Let each commodity `c` follow a route: a list of links forming a walk from its origin to its
destination, each link starting at the junction where the previous one ends. If commodity `c`
carries flow only from a link of its route to the next link of the route (`q(c, e, e') ≠ 0` implies
that `(e, e')` are consecutive in the list), then `q(c, e, e') = 0` whenever `head e ≠ tail e'`.
