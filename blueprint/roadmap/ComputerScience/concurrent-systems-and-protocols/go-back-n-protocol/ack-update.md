# Sender update on an acknowledgement

For a go-back-N sender with window base $b$, $c$
outstanding messages and next-frame offset $o$, and an acknowledgement $k$, let
$d = \max(k + 3 - b, 0) \bmod 3$. If $1 \le d \le c$, the window slides: the new sender has
base $k$, $c - d$ outstanding messages and next-frame offset $\max(o - d, 0)$. Otherwise the
sender is unchanged.
