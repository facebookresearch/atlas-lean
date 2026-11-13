# Patience scan

Given an array of tails and a list over a linear order, the patience scan
applies the patience step to the elements of the list in order: on the empty list it returns the
tails unchanged, and on a list $x$ followed by $xs$ it applies the patience step for $x$ to the
tails and then runs the patience scan of $xs$ from the result. Its cost is the total cost of the
steps.
