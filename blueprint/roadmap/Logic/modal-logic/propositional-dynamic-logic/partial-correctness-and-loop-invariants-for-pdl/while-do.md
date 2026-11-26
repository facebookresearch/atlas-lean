# Guarded while loop in PDL

For a formula $g$ (the guard) and a program $a$ (the body), the program
$\mathbf{while}\ g\ \mathbf{do}\ a$ is $(g? ; a)^* ; (\neg g)?$: it iterates the guarded body and
then tests that the guard is false.
