# Method body lookup

For a class table, a method name $m$ and a class name $C$, method body lookup returns nothing when [method lookup](lookup-method.md) finds no declaration of $m$ from $C$; otherwise it returns the parameter names of the method found, in order, and its body (MB-CLASS, MB-SUPER).
