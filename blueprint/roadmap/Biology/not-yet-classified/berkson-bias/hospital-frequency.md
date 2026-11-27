# Hospital Frequency

The frequency of disease `c` among admitted persons whose disease set satisfies `G`:
`∑_{S ∈ G, c ∈ S} P(S, admitted) / ∑_{S ∈ G} P(S, admitted)`. It is meaningful when the group has
positive admitted mass; if that mass is `0`, Lean's convention `x / 0 = 0` makes the value `0`.
