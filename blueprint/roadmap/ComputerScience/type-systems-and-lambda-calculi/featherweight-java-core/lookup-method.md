# Method lookup

Walks the superclass chain of `C` upward, skipping `Object` and classes without a declaration, and returns the first method declaration named `m` found in a declaration on the way (within a class, the first method with that name), or nothing. It returns the method declaration, not the class that declares it (MB-CLASS/MB-SUPER).
