# Short universal recovery menus exist for line-parity codes

Let $K$ have $q = 2^b$ elements, $L = \ell b$ (bits per point of $K^\ell$), and $0 < k \le g$. If $512\, g\, q \le q^{\ell - 1}$, then there is a menu of

$$r = \Bigl\lfloor \frac{g(1 + 3L)}{k} \Bigr\rfloor + 1$$

tuples of nonzero directions for $k$ requests that is universal for $g$ occupied lines: for every list of at most $g$ occupied lines and every $k$ targets, some menu entry leaves at least half of the requests clean. Evaluating the whole menu examines at most $g(1 + 3L) + k$ candidate lines.

## Proof sketch

Under the budget, a uniformly random tuple of nonzero directions leaves fewer than half the requests clean with probability at most $2^{-k}$ in every fixed state: a collision cut selects a quarter of the requests whose lines collide, and conditional counting over the selected coordinates bounds the bad tuples by a product. There are at most $2^{g(1 + 3L)}$ states, so a union bound over $r$ independent entries shows some menu works for all states.

## Depends on

- [Line-parity codes and universal recovery menus](line-parity-code.md)

## Sources

- S. Schlesinger, "Boolean circuit mass production", 2026.
