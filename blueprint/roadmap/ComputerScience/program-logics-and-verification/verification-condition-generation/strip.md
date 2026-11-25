# Erasing annotations

The IMP command $\mathrm{strip}(C)$ underlying an annotated command
$C$ is obtained by deleting the invariant of every while loop: skip, assignments, sequential
composition and conditionals are kept with their parts stripped, and
$\{I\}\ \mathrm{while}\ b\ \mathrm{do}\ C'$ becomes
$\mathrm{while}\ b\ \mathrm{do}\ \mathrm{strip}(C')$.
