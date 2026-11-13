# Is IPWNull Calibrated

The p-values `p` are **calibrated for the observed-data IPW null**: for every endpoint `j`,
`p j` is valid whenever its observed outcome `Y j` satisfies `IsIPWNull`. This is a property
of the observed data and the test, with no dependence on potential outcomes or `ateNulls`.
