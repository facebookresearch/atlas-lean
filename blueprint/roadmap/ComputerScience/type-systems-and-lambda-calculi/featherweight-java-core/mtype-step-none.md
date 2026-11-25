# Method type lookup falls back to the superclass

Let the class table `ct` be well formed and `C` a class with declaration `cd`.
If `cd` declares no method named `m`, the method type of `m` in `C` is the
method type of `m` in the superclass of `cd` (rule MT-SUPER).
