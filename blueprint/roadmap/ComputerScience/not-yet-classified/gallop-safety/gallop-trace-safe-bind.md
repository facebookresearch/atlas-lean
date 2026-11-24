# Gallop Trace Safe bind

Sequentially composing two successful, safe traced computations preserves
all shared trace obligations, including the absence of pending-stack pushes.
