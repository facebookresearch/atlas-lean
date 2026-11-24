# Total-count sets are reaction-closed when reactions conserve the count

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and any reaction set `ρ`, in which every reaction conserves the total
molecule count: `∑_s src(r)_s = ∑_s prod(r)_s` for every reaction `r`. Then for every `n ∈ ℕ` the
[set](total-class.md) of states with total count `n` is [reaction-closed](is-reaction-closed.md).
Every reaction vector of such a network has coordinate sum `0`, so each
[compatibility class](compat-class.md) lies inside one of these sets.
