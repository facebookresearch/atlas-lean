# Method body lookup falls back to the superclass

Let the class table `ct` be well formed and `C` a class with declaration `cd`.
If `cd` declares no method named `m`, the method body of `m` in `C` is the
method body of `m` in the superclass of `cd` (rule MB-SUPER).
