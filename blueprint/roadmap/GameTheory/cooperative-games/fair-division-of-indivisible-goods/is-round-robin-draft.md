# Is Round Robin Draft

Fix an order of `n ≥ 1` agents. A chronological bijection `pick` from turns to goods is a
round-robin draft if, at each zero-based turn `t`, the agent at position `t % n` in that order
weakly prefers `pick t` to every good in the suffix starting at `t`. This suffix consists of
exactly the remaining goods, so any maximiser may be chosen and all goods are taken.
