# Left-variable currying evaluates on pure tensor classes

Left-variable currying evaluates on pure tensor classes.

For `a : A` and `b : B`, the map obtained by left-variable currying satisfies `(groupCurryLeft
f b)(a) = f([a ⊗ b])`.
