# Linear Step

The raw synchronous linear control of Chiu--Jain Section 1.3:
`x i := aI + bI * x i` on increase and `x i := aD + bD * x i` on decrease,
with overload exactly when the total exceeds `goal`. There is no clipping
in the raw law. Increasing at equality (`total x = goal` takes the
increase branch) is a declared convention: the paper distinguishes strict
overload and strict underload without assigning equality.
