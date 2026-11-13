# Every position has a unique innermost strict container

**Every position has a unique innermost strict container** (not loop membership): a
position `x` either lies strictly inside no pair, or there is a unique pair `p` with
`p.1 < x < p.2` such that no branch of `p` has `x` strictly inside it. This is an
innermost-container assignment, not the conventional loop decomposition of positions:
endpoints are excluded from the loop they close (a position `x = q.1` or `x = q.2` is
assigned to the loop of which `q` is a branch, never to the loop closed by `q`), and no
`x < s.length` hypothesis is assumed, so positions outside the sequence fall in the
first (exterior) case. In particular do not read this as saying loops uniquely decompose
positions; see `existsUnique_closing_pair` for the closing-pair side of the convention.
