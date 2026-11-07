# Tait reducibility for closed terms

Reducibility of a closed term $t$ is defined by
recursion on its simple type. At a base type, $t$ is reducible when it terminates. At a function
type $A \Rightarrow B$, $t$ is reducible when it terminates and, for every reducible closed term
$a$ of type $A$, the application $t\,a$ is reducible.
