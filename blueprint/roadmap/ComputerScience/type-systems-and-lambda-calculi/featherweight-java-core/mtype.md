# Method type lookup

For a class table, a method name $m$ and a class name $C$, method type lookup returns nothing when [method lookup](lookup-method.md) finds no declaration of $m$ from $C$; otherwise it returns the parameter classes of the method found, in order, and its return class (MT-CLASS, MT-SUPER).
